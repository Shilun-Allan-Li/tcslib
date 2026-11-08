<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Majority.lean :: BooleanAnalysis.ThresholdFunctions.sum_pow_mul_le_of_prefix_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix domination for geometric weights

**Claim.** If the prefix sums of $b$ are bounded above by those of $a$, their total sums agree through $N-1$, and $0\le\rho\le1$, then weighting their terms by $\rho^k$ preserves the inequality in favor of $a$.

**Proof.** Set $d_k=a_k-b_k$. The prefix hypothesis says each partial sum $D_j=\sum_{k<j}d_k$ is nonnegative, while equality of the total sums gives $D_N=0$. Abel summation rewrites the weighted difference as
\[
\sum_{k<N}\rho^k d_k=\sum_{i<N-1}(\rho^i-\rho^{i+1})D_{i+1}.
\]
Each partial sum on the right is nonnegative. Also $\rho^i\ge\rho^{i+1}$ because $\rho^{i+1}=\rho^i\rho$ and $0\le\rho\le1$. Hence every term on the right is nonnegative, so the weighted sum of $a$ is at least that of $b$.
