<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.tendsto_sqrt_gLog_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square-root Gaussian tail asymptotics

**Claim.** For the standard Gaussian cumulative distribution function $\Phi$ and $L(t)=2\log(1/\Phi(t))$, the ratio $\sqrt{L(t)}/(-t)$ tends to $1$ as $t\to-\infty$.

**Proof.** The quadratic asymptotic gives $L(t)/t^2\to1$. The square-root function is continuous at $1$, so $\sqrt{L(t)/t^2}\to1$. For negative $t$, positivity of $L(t)$ and the identity $\sqrt{t^2}=|t|=-t$ show that $\sqrt{L(t)/t^2}=\sqrt{L(t)}/(-t)$. This equality holds eventually as $t\to-\infty$, giving the claimed limit.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.tendsto_gLog_div_sq`, `BooleanAnalysis.ThresholdFunctions.gLog_pos`.
