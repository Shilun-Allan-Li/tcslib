<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell.lean :: BooleanAnalysis.GaussianSpace.rotationSensitivity_borell -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian rotation sensitivity bound

**Claim.** For a measurable set and every angle between zero and π/2, twice the difference between its Gaussian measure and the Gaussian halfspace stability at correlation cos θ is at most its rotation sensitivity.

**Proof.** Write α for the Gaussian measure of the set; it lies in [0,1]. At θ=0, the halfspace stability at correlation 1 equals α, so the left side is zero and the bound follows. At θ=π/2, the halfspace stability at correlation 0 equals α², and the rotation sensitivity is 2α(1−α); these give equality. For an interior angle, ρ=cos θ lies strictly between zero and one. Apply Borell's inequality (`borell`) to the indicator of the set: its Gaussian noise stability at ρ is at most the halfspace stability at ρ and measure α. The identity relating rotation sensitivity to noise stability (`rotationSensitivity_eq_stability`) rewrites the desired left side using that same noise stability. The comparison from Borell then gives the claimed inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianHalfspaceStability_one`, `BooleanAnalysis.GaussianSpace.gaussianHalfspaceStability_zero`, `BooleanAnalysis.GaussianSpace.borell`, `BooleanAnalysis.GaussianSpace.rotationSensitivity_eq_stability`, `BooleanAnalysis.GaussianSpace.rotationSensitivity_pi_div_two`.
