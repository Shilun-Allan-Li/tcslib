<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SmoothVariation.lean :: BooleanAnalysis.GaussianSpace.lintegral_gaussianGradient_le_of_integral_variation_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gradient bound from mean rotational variation

**Claim.** If $f$ takes values in $[0,1]$ and its scaled mean rotational variation is bounded by $C$ for every positive angle, then the extended Gaussian integral of its gradient norm is at most $C$.

**Proof.** Everywhere differentiability implies continuity of $f$. Since $0\le f\le1$, the difference between any two values of $f$ has absolute value at most one. Thus the rotational difference is integrable under the probability measure on pairs of independent Gaussian vectors: it is measurable by continuity and bounded by the integrable constant one. Convert the real integral of its absolute value, multiplied by $\sqrt{\pi/2}/\theta$, to the corresponding extended nonnegative integral. The assumed bound then supplies exactly the rotational-integral hypothesis of the Gaussian gradient estimate (\texttt{BooleanAnalysis.GaussianSpace.lintegral_gaussianGradient_le}); applying it gives the claimed bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.lintegral_gaussianGradient_le`.
