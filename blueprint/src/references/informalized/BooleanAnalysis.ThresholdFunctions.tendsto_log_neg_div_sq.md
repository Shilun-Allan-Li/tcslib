<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.tendsto_log_neg_div_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithm dominated by the square

**Claim.** As $t\to-\infty$, $\log(-t)/t^2$ tends to zero.

**Proof.** As $u\to+\infty$, $\log u/u\to0$ by the standard fact that the logarithm grows sublinearly, and $1/u\to0$. Their product therefore tends to zero. Substitute $u=-t$, which tends to $+\infty$ as $t\to-\infty$; the product is $\log(-t)/(-t)^2=\log(-t)/t^2$.
