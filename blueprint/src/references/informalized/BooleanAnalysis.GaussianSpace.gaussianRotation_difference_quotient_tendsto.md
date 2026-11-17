<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SmoothVariation.lean :: BooleanAnalysis.GaussianSpace.gaussianRotation_difference_quotient_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute rotation quotient limit

**Claim.** As the angle tends to zero through positive values, the absolute rotation difference quotient converges to $|L(y)|$.

**Proof.** Consider the one-variable function $g(\theta)=f(\cos\theta\,x+\sin\theta\,y)$. The chain rule gives $g'(0)=L(y)$, so the difference quotient $(g(\theta)-g(0))/\theta$ tends to $L(y)$ from the right. Continuity of absolute value then makes its absolute value tend to $|L(y)|$. Since $\theta>0$, the given quotient $|g(\theta)-g(0)|/\theta$ equals that absolute difference quotient, proving the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianRotation_comp`.
