<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/MeanBound.lean :: BooleanAnalysis.GaussianSpace.norm_integral_le_toReal_eLpNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral bounded by the $L^p$ norm

**Claim.** On a probability space, if $p\geq1$ and $f\in L^p(\mu)$, then $\left|\int f\,d\mu\right|\leq\|f\|_{L^p(\mu)}$.

**Proof.** The norm of the integral is bounded by the integral of the pointwise norm, so $\left|\int f\,d\mu\right|\leq\int |f|\,d\mu$. Since the measure is a probability measure, the right side is the $L^1$ norm of $f$. Monotonicity of $L^p$ norms on a probability space, for $1\leq p$, bounds this by the $L^p$ norm. The membership assumption ensures the relevant norms are finite, and translating the extended norm to its real value gives the stated inequality.
