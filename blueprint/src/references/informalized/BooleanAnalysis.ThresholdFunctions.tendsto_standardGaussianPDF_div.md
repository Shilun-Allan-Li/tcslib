<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.tendsto_standardGaussianPDF_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Density and Tail Asymptotic

**Claim.** As $t\to-\infty$, the standard Gaussian density divided by the product of its cumulative distribution function and $\sqrt{L(t)}$ tends to $1$.

**Proof.** The inverse Mills ratio tends to $1$ at negative infinity (`tendsto_millsRatio`), and so does the reciprocal of $\sqrt{L(t)}/(-t)$, by the limit for that latter ratio (`tendsto_sqrt_gLog_div`). Their product therefore tends to $1$. For all sufficiently negative $t$, the quantities in the denominators are nonzero: $L(t)>0$, the cumulative distribution function is positive, and the density is positive. Using the definition of the Mills ratio, the product just considered agrees there with $\varphi(t)/(\Phi(t)\sqrt{L(t)})$; hence this target ratio has the same limit.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.tendsto_millsRatio`, `BooleanAnalysis.ThresholdFunctions.tendsto_sqrt_gLog_div`, `BooleanAnalysis.ThresholdFunctions.gLog_pos`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_pos`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.
