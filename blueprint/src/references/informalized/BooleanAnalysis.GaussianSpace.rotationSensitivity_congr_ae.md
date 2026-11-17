<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SurfaceArea.lean :: BooleanAnalysis.GaussianSpace.rotationSensitivity_congr_ae -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sensitivity under Gaussian null changes

**Claim.** If two sets agree almost everywhere for standard Gaussian measure, then their rotation sensitivities agree for every angle.

**Proof.** Let μ be standard Gaussian measure on the cube. The hypothesis says membership in the two sets agrees for μ-almost every first coordinate. Under the product measure μ×μ, the first coordinate still has law μ, so the same agreement holds for almost every pair. Moreover, the Gaussian rotation map preserves μ×μ (`measurePreserving_gaussianRotation`); applying that preservation to the null exceptional set shows that membership also agrees for almost every rotated point. Outside the union of these two exceptional sets, both the original point and its rotated point have the same membership status in the two sets. Consequently, the events that membership changes under rotation coincide almost everywhere, so they have equal measure and hence equal sensitivities.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianRotation`.
