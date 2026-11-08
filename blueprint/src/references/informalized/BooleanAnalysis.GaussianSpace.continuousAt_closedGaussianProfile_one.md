<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.GaussianSpace.continuousAt_closedGaussianProfile_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity at probability one

**Claim.** The closed Gaussian profile is continuous at $1$.

**Proof.** Consider the profile after the change of variable $p\mapsto 1-p$. This map is continuous and sends $p=1$ to $0$, so continuity of the profile at $0$ implies continuity of this composite at $1$. The profile is symmetric under complementation: its value at $1-p$ equals its value at $p$. Thus the composite is the original profile, proving continuity at $1$.

**Key facts.** `BooleanAnalysis.GaussianSpace.continuousAt_closedGaussianProfile_zero`, `BooleanAnalysis.GaussianSpace.closedGaussianProfile_one_sub`.
