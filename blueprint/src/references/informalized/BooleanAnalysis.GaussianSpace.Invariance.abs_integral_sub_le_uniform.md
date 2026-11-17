<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.abs_integral_sub_le_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation stability under uniform approximation

**Claim.** On a probability space, if $f$ is integrable, $g$ is measurable up to a null set, and $|f-g|\le D$ everywhere, then the expectations of $f$ and $g$ differ by at most $D$ in absolute value.

**Proof.** The pointwise bound gives $\|f-g\|\le D$ almost everywhere. Since the constant function with value $D$ is integrable on a probability space, this bound together with the almost-everywhere measurability of $g$ and integrability of $f$ implies that $g$ is integrable. Thus the difference of the integrals is the integral of $f-g$. The norm bound for an integral, applied to $f-g$, bounds its absolute value by the integral of the constant $D$. That integral is $D$, because the measure of the whole space is one.
