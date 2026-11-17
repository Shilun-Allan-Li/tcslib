<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.tendsto_sqrt_mul_log_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing square-root logarithmic power

**Claim.** For every natural number $d$, as $\delta$ tends to zero through positive values, $\sqrt{\delta}\,\bigl(\log(1/\delta)\bigr)^d$ tends to zero.

**Proof.** Use the standard little-$o$ estimate at zero that $|\log\delta|^d=o(\delta^{-1/2})$, equivalently that $\delta^{-1/2}$ grows faster than the $d$th power of the logarithm. Its quotient formulation says $|\log\delta|^d/\delta^{-1/2}\to0$. For sufficiently small positive $\delta<1$, the logarithm is nonpositive and $|\log\delta|=\log(1/\delta)$; also $\delta^{-1/2}=1/\sqrt{\delta}$. Thus this quotient is exactly $\sqrt{\delta}\,\bigl(\log(1/\delta)\bigr)^d$, proving the limit.
