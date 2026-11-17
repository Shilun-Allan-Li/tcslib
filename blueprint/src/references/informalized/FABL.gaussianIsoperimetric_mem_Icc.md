<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.gaussianIsoperimetric_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range Bound for the Profile

**Claim.** For every α in the unit interval, the Gaussian isoperimetric function lies between 0 and (2π)^{-1/2}.

**Proof.** Split according to whether α lies in (0,1). In the interior case, the profile equals the standard Gaussian density at the associated upper quantile. The density is nonnegative, and its value is at most its peak, (2π)^{-1/2} (standardGaussianDensity_le_peak). In the other case, the profile is zero by definition, which lies in the stated interval because (2π)^{-1/2} is nonnegative.

**Key facts.** `FABL.gaussianIsoperimetric_apply_of_mem_Ioo`, `FABL.standardGaussianDensity_le_peak`.
