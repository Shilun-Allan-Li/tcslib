<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.tendsto_cube_atBot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic divergence at negative infinity

**Claim.** As $x$ tends to $-\infty$, $x^3$ also tends to $-\infty$.

**Proof.** For all sufficiently negative $x$, in particular for $x\le-1$, one has $x^2\ge1$. Hence $x^3=x\,x^2\le x$, since $x$ is nonpositive. The identity function tends to $-\infty$ as $x$ does, and a function bounded above by it on a tail also tends to $-\infty$. Therefore $x^3\to-\infty$.
