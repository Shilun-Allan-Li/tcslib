<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.kane_noise_aux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block-Count Polylogarithmic Estimate

**Claim.** For the specified $E,\delta,k,d$ and $m=\mathrm{noiseBlockCount}(\delta)$, the displayed block-count expression is bounded by the stated multiple of $\sqrt\delta\,(\log(1/\delta))^d$.

**Proof.** Write $M=\mathrm{noiseBlockCount}(\delta)$ and $L=\log(1/\delta)$. The block-count bounds (`noiseBlockCount_spec`) give $2\le M\le1/\delta$ and $1/(2\delta)\le M$. In particular, $2\le1/\delta$, so logarithmic monotonicity gives $\log 2\le L$ and $\log(\max\{M,2\})\le L$. The auxiliary estimate (`rpow_le_log_two_rpow_mul_pow`) then bounds $L^E$ by $(\log 2)^{-d}L^d$. Using monotonicity of real powers for nonnegative bases and $E\ge0$, bound the original real power by $(2^kL)^E$. Multiplicativity of real powers splits this as $(2^k)^E L^E$, after which the auxiliary estimate bounds it by $(2^k)^E(\log 2)^{-d}L^d$. Finally, the square-root block estimate (`sqrt_div_noiseBlockCount_le`) gives $\sqrt M/M\le\sqrt2\sqrt\delta$. Multiplying these nonnegative bounds yields the claimed inequality.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.sqrt_div_noiseBlockCount_le`, `BooleanAnalysis.ThresholdFunctions.noiseBlockCount_spec`, `BooleanAnalysis.ThresholdFunctions.rpow_le_log_two_rpow_mul_pow`.
