<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean :: Complexity.LogProg.markI_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marking an empty integer interval

**Claim.** For integers $a,z$, marking $z$ relative to the interval from $a$ to $a-1$ returns true exactly when $z=0$, and is undefined otherwise.

**Proof.** By definition, the marker first returns `some true` when $z=0$. In the other case it could return `some false` only if $a\le z\le a-1$. No integer satisfies both inequalities, so that branch is impossible and the result is `none`.
