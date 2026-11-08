<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.GaussianSpace.continuousAt_closedGaussianProfile_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity at probability zero

**Claim.** The closed Gaussian profile is continuous at $0$.

**Proof.** Check continuity from each side. On the left of $0$, the profile is constantly zero: those points lie outside the open interval $(0,1)$, and its value at $0$ is also zero. On the right, the profile tends to zero by the stated right-hand limit theorem. The matching one-sided continuities give continuity at $0$.

**Key facts.** `BooleanAnalysis.GaussianSpace.closedGaussianProfile_zero`, `BooleanAnalysis.GaussianSpace.tendsto_closedGaussianProfile_zero`.
