<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.noiseSensitivity_le_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Sensitivity Upper Bound

**Claim.** For any Boolean-cube function $f$ and $\delta\le1/2$, the noise sensitivity satisfies $\operatorname{NS}_{\delta}(f)\le1/2$.

**Proof.** The parameter $\rho=1-2\delta$ is nonnegative by the assumed bound on $\delta$. Nonnegativity of noise stability at nonnegative parameter (\texttt{BooleanAnalysis.ThresholdFunctions.noiseStability_nonneg}) gives $\operatorname{Stab}_{1-2\delta}(f)\ge0$. Substituting this into $\operatorname{NS}_{\delta}(f)=(1-\operatorname{Stab}_{1-2\delta}(f))/2$ yields $\operatorname{NS}_{\delta}(f)\le1/2$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.noiseStability_nonneg`.
