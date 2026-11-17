<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ContinuousReasonableness.lean :: FABL.integral_pow_uniformIntervalMeasure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moments of the uniform interval law

**Claim.** For every natural number $m$, the $m$th moment of the probability distribution obtained by restricting Lebesgue measure to $[-1,1]$ and normalizing is $\frac12\int_{-1}^{1}x^m\,dx$.

**Proof.** Unfolding the definitions, the measure is Lebesgue measure on $[-1,1]$ scaled by the reciprocal of the interval's volume. Since that volume is $2$, integrating $x^m$ against the normalized restriction gives one half of its integral over the interval. The interval integral over $[-1,1]$ is the same as the oriented integral from $-1$ to $1$, which is exactly the defining expression for the stated moment.
