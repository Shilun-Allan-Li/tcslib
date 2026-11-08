<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.lowDegree_oneSided_anticoncentration -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-sided anticoncentration

**Claim.** If $f$ has positive variance and degree at most $k$, then $\Pr[f>\mathbb E f]\ge \exp(-2k)/4$.

**Proof.** Center the function by setting $g=f-\mathbb E f$. Linearity of expectation and the fact that constants have their expected value show that $\mathbb E g=0$. Subtracting a constant preserves the degree bound. The low-degree $L^1$–$L^2$ estimate gives $e^{-2k}\langle g,g\rangle\le(\mathbb E|g|)^2$, while the centered absolute-moment estimate gives $(\mathbb E|g|)^2\le4\langle g,g\rangle\Pr[g>0]$. Combining these inequalities and using $\langle g,g\rangle=\operatorname{Var}(f)>0$, divide by this positive variance and by $4$ to obtain $e^{-2k}/4\le\Pr[f>\mathbb E f]$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_sub`, `BooleanAnalysis.ThresholdFunctions.expect_const`, `BooleanAnalysis.Hypercontractivity.has_degree_at_most_sub_const`, `BooleanAnalysis.Hypercontractivity.lowDegree_l1_l2_sq`, `BooleanAnalysis.Hypercontractivity.centered_abs_expect_sq_le`.
