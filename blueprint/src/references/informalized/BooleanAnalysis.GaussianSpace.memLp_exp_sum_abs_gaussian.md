<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Exponential.lean :: BooleanAnalysis.GaussianSpace.memLp_exp_sum_abs_gaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Exponential Integrability in Every Finite Degree

**Claim.** For finite $p\in[0,\infty]$, the function $x\mapsto\exp\!\left(c\sum_{i=1}^n|x_i|\right)$ belongs to $L^p$ under product standard Gaussian measure.

**Proof.** If $p=0$, membership follows from the continuous function being measurable, since $L^0$ membership only requires almost-everywhere strong measurability. For $p>0$, the finite-exponent membership criterion reduces the claim to integrability of the $p$th power of the function's norm. The exponential is positive, so that power is $\exp\!\left(cp\sum_i|x_i|\right)$. This is integrable by the Gaussian exponential-integrability result, applied with parameter $cp$.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_exp_sum_abs_gaussian`.
