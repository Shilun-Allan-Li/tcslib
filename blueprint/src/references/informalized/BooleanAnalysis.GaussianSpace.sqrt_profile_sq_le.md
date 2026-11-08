<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov.lean :: BooleanAnalysis.GaussianSpace.sqrt_profile_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity After Adding a Squared Coordinate

**Claim.** If the closed Gaussian profile at $\E[f]$ is at most the Bobkov functional of $f$, then for every real $d$, $\sqrt{\overline I(\E[f])^2+d^2}\le\sqrt{B(f)^2+d^2}$.

**Proof.** The closed Gaussian profile is nonnegative (`BooleanAnalysis.GaussianSpace.closedGaussianProfile_nonneg`). By hypothesis it is at most the Bobkov functional, so both quantities are nonnegative and their squares are ordered in the same way. Adding $d^2$ preserves that order. Taking square roots, which is monotone on nonnegative reals, proves the inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.closedGaussianProfile_nonneg`.
