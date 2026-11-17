<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/StableInfluence.lean :: FABL.noiseSensitivityCurve_eq_noiseSensitivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Sensitivity Curve Identity

**Claim.** For a Boolean function and $0\le\delta\le1$, the noise sensitivity curve of its real-valued version equals its noise sensitivity at rate $\delta$.

**Proof.** Replace the stability curve in the definition of the noise sensitivity curve by noise stability, using the identity between these quantities (`stabilityCurve_eq_noiseStability`) at parameter $1-2\delta$. The noise sensitivity and noise stability relation (`noiseSensitivity_eq_half_sub_half_noiseStability`) says that the latter expression is exactly the noise sensitivity. Reversing that equality proves the claim.

**Key facts.** `FABL.stabilityCurve_eq_noiseStability`, `FABL.noiseSensitivity_eq_half_sub_half_noiseStability`.
