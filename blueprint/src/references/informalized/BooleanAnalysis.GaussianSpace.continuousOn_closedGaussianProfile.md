<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.GaussianSpace.continuousOn_closedGaussianProfile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity on the probability interval

**Claim.** The closed Gaussian profile is continuous on $[0,1]$.

**Proof.** Fix a point $a\in[0,1]$. If $a=0$, continuity follows from continuity at zero; if $a=1$, it follows from continuity at one. In the remaining case $0<a<1$, the profile has a derivative at $a$, so it is continuous there. In each case, continuity at the point implies continuity relative to $[0,1]$.

**Key facts.** `BooleanAnalysis.GaussianSpace.continuousAt_closedGaussianProfile_zero`, `BooleanAnalysis.GaussianSpace.continuousAt_closedGaussianProfile_one`, `BooleanAnalysis.GaussianSpace.hasDerivAt_closedGaussianProfile`.
