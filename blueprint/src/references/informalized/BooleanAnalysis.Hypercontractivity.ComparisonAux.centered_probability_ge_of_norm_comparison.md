<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.centered_probability_ge_of_norm_comparison -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive-support probability estimate

**Claim.** Let $P$ be a product of $n$ finite probability spaces with strictly positive coordinate weights summing to one. If a real function $g$ has expectation zero and positive second moment, and $C>0$ satisfies $\|g\|_{2,P}\le C\|g\|_{1,P}$, then $1/(4C^2)\le \Pr_P(g>0)$.

**Proof.** Write the product mass at a point as the product of its coordinate weights; it is nonnegative. The norm definitions give $\|g\|_{2,P}=\sqrt{\mathbb E_P[g^2]}$. The weighted centered absolute-sum inequality (`FiniteNorms.centered_abs_sum_sq_le`) applied to the product masses and the zero-mean hypothesis gives $\bigl(\mathbb E_P|g|\bigr)^2\le4\mathbb E_P[g^2]\Pr_P(g>0)$. Squaring the assumed norm comparison and substituting the expression for the second norm gives $\mathbb E_P[g^2]\le C^2\bigl(\mathbb E_P|g|\bigr)^2$. Combining the two inequalities yields $\mathbb E_P[g^2]\le4C^2\mathbb E_P[g^2]\Pr_P(g>0)$. The second moment and $C$ are positive, so cancellation and rearrangement prove the stated lower bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteNorms.centered_abs_sum_sq_le`.
