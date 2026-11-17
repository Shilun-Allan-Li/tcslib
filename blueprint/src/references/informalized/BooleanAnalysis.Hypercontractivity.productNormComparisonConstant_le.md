<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.productNormComparisonConstant_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison constant upper bound

**Claim.** For $0<\lambda\le1/2$, the comparison constant satisfies $C(\lambda)\le e/\sqrt{2\lambda}$.

**Proof.** First handle $\lambda=1/2$: the definition gives $C(\lambda)=e$, and the right side is also $e$. Otherwise $1-2\lambda>0$, so both sides are positive and logarithms preserve the inequality. Taking logarithms and expanding the real powers reduces the claim to an inequality between logarithms of $1-\lambda$, $\lambda$, and $2\lambda$. Use the standard bounds $\log t\le t-1$ for $t>0$ and $t-1\le\log t$ in the equivalent reciprocal form (the latter is `one_sub_inv_le_log_of_pos`). Multiplying the reciprocal-form inequality by the positive quantity $2\lambda$ and combining the resulting bounds yields the required logarithmic inequality by elementary algebra. Exponentiating recovers the claimed bound.
