<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Walks.lean :: Expander.norm_resVec_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted-Vector Norm Bound

**Claim.** For each $k\ge0$, the iterated restricted vector satisfies $\|r_k\|\le((1-\lambda)\sqrt{\beta}+\lambda)^k\|r_0\|$.

**Proof.** Proceed by induction on $k$. At $k=0$, both sides are equal. For the induction step, the recursion gives $r_{k+1}=A_Br_k$. The one-step estimate for the restricted matrix (`norm_toCLM_resMatrix_le`) bounds its norm by $((1-\lambda)\sqrt{\beta}+\lambda)\|r_k\|$. The factor is nonnegative because $\lambda\le1$, $\sqrt{\beta}\ge0$, and $\lambda\ge0$. Thus the induction hypothesis can be multiplied by this factor without reversing the inequality. Combining the resulting bounds and using the law of exponents gives the stated estimate at $k+1$.

**Key facts.** `Expander.norm_toCLM_resMatrix_le`.
