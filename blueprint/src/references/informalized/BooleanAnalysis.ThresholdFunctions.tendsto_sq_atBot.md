<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.tendsto_sq_atBot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squares diverge at negative infinity

**Claim.** The function $x\mapsto x^2$ tends to $+\infty$ as $x\to-\infty$.

**Proof.** The absolute value $|x|$ tends to $+\infty$ as $x\to-\infty$. The product of two functions tending to $+\infty$ also tends to $+\infty$, so $|x|\,|x|\to+\infty$. Since $|x|^2=x^2$, the result follows.
