<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.sqrt_add_le_add_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subadditivity of the square root

**Claim.** For nonnegative real numbers $x,y$, one has $\sqrt{x+y}\le\sqrt{x}+\sqrt{y}$.

**Proof.** Both sides are nonnegative, so it suffices to compare their squares. The square of the right side is $x+y+2\sqrt{x}\sqrt{y}$, which is at least $x+y$, since the square roots are nonnegative. Taking square roots yields the inequality.
