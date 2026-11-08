<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SurfaceArea.lean :: BooleanAnalysis.GaussianSpace.surfaceArea_congr_ae -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Surface Area Respects Null Changes

**Claim.** If two measurable sets agree almost everywhere under standard Gaussian measure, then they have the same Gaussian surface area.

**Proof.** The rotation sensitivity of the two sets agrees at every angle whenever the sets agree almost everywhere (`rotationSensitivity_congr_ae`). Gaussian surface area is defined as the lower limit, as the angle decreases to zero, of a scaled expression in rotation sensitivity. Since the two sensitivity functions agree pointwise in the angle, their scaled expressions and hence their lower limits agree.

**Key facts.** `BooleanAnalysis.GaussianSpace.rotationSensitivity_congr_ae`.
