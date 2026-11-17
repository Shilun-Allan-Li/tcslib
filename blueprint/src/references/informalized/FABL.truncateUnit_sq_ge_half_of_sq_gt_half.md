<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLCounterexample.lean :: FABL.truncateUnit_sq_ge_half_of_sq_gt_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truncated Square Lower Bound

**Claim.** If $z^2>1/2$, then the square of the projection of $z$ onto $[-1,1]$ is at least $1/2$.

**Proof.** If $z\le -1$, its projection is $-1$, whose square is $1$. If this fails but $z\ge 1$, its projection is $1$, again with square $1$. Otherwise $z$ lies in $[-1,1]$, so projection leaves it unchanged; the desired inequality is then exactly the given hypothesis, weakened from strict to non-strict.
