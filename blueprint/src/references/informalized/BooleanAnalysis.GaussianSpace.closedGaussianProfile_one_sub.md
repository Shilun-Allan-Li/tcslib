<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.GaussianSpace.closedGaussianProfile_one_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflection symmetry of the profile

**Claim.** For every real number $a$, the closed Gaussian profile at $1-a$ equals its value at $a$.

**Proof.** Split into two cases. If $a\in(0,1)$, then the inequalities $0<a<1$ imply $0<1-a<1$. On both inputs the closed Gaussian profile therefore equals the Gaussian isoperimetric profile (closedGaussianProfile_eq); reflection symmetry of that profile, $U(1-a)=U(a)$ (gaussianIsoperimetric_one_sub), gives the result. If $a\notin(0,1)$, then $1-a\notin(0,1)$ as well: otherwise the inequalities for $1-a$ would imply $0<a<1$. The closed profile is $0$ at both inputs, so the equality follows.

**Key facts.** `BooleanAnalysis.GaussianSpace.closedGaussianProfile_eq`, `BooleanAnalysis.ThresholdFunctions.gaussianIsoperimetric_one_sub`.
