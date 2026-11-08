<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.accessCfg_safe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safety of an Access Configuration

**Claim.** In the specified access configuration, each work-head position lies between $-1$ and the length of the binary expansion of $|y|+1$, inclusive.

**Proof.** Fix one of the four work tapes. If its index is $2$, the update defining the head positions assigns it the specified value $q$, and the two assumed inequalities give the required bounds. At any other index, the update leaves the default position $0$ unchanged; since $0$ lies between $-1$ and the nonnegative binary-expansion length, the bounds hold there as well.
