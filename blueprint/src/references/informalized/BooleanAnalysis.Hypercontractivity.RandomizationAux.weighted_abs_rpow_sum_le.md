<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.weighted_abs_rpow_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Absolute-Power Inequality

**Claim.** For nonnegative weights summing to one and $q\ge1$, the $q$th power of the absolute weighted average of $F$ is at most the weighted average of $|F|^q$.

**Proof.** The triangle inequality for a finite sum gives $\left|\sum_a w(a)F(a)\right|\le\sum_a|w(a)F(a)|$. Since each weight is nonnegative, the right side is $\sum_a w(a)|F(a)|$. Raising both nonnegative sides to the power $q$ preserves the inequality. The weighted power-mean inequality, applied to the nonnegative values $|F(a)|$ with weights summing to one and $q\ge1$, bounds $\left(\sum_a w(a)|F(a)|\right)^q$ by $\sum_a w(a)|F(a)|^q$. Combining these two bounds proves the result.
