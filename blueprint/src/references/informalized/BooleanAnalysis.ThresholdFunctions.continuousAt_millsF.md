<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.continuousAt_millsF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Mills Function

**Claim.** For every nonzero real number $t$, the Mills function $x\mapsto\varphi(x)(x^{-3}-x^{-1})$ is continuous at $t$.

**Proof.** At a nonzero $t$, the function $x\mapsto x^3$ is continuous and nonzero, so its reciprocal is continuous there. The reciprocal function $x\mapsto x^{-1}$ is also continuous at every nonzero point. Their difference is therefore continuous at $t$. The standard Gaussian density is continuous everywhere (`continuous_standardGaussianPDF`), so multiplying it by this difference preserves continuity at $t$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.continuous_standardGaussianPDF`.
