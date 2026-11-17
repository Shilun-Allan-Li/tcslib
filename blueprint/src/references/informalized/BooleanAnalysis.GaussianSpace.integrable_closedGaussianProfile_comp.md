<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.GaussianSpace.integrable_closedGaussianProfile_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Gaussian Profile Composition

**Claim.** If a measurable function on a finite measure space takes values in $[0,1]$, then composing it with the closed Gaussian profile gives an integrable function.

**Proof.** The closed Gaussian profile is continuous on the compact interval $[0,1]$, so it is bounded there: choose $M$ with absolute value at most $M$ throughout that interval. Its global continuity also makes its composition with the measurable function measurable. Since the function's values lie in $[0,1]$, the composition is bounded almost everywhere by $M$. A measurable function bounded by a constant on a finite measure space is integrable, proving the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.continuousOn_closedGaussianProfile`, `BooleanAnalysis.GaussianSpace.continuous_closedGaussianProfile`.
