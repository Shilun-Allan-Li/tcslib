<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/SparseSampling.lean :: BooleanAnalysis.ThresholdFunctions.spectralOneNorm_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive spectral one-norm

**Claim.** If a real-valued function on the Boolean cube is not identically zero, then its spectral one-norm is strictly positive.

**Proof.** The spectral one-norm is nonnegative. Suppose it were zero. Since it is a finite sum of nonnegative absolute values, every summand must be zero, so every Fourier coefficient vanishes. The Walsh expansion identity (BooleanAnalysis.walsh_expansion) expresses the value of the function at each point as the sum of its Fourier coefficients multiplied by the corresponding characters. If all coefficients vanish, this identity makes the function zero at every point, contradicting the hypothesis that it is not identically zero. Thus the nonnegative spectral one-norm cannot be zero, and must be strictly positive.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.spectralOneNorm_nonneg`, `BooleanAnalysis.walsh_expansion`.
