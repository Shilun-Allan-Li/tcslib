<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.matchingStirlingCore_isTheta_growth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic matching core growth

**Claim.** For every positive integer $r$, the matching Stirling core and matching core growth have the same asymptotic order as $k$ tends to infinity.

**Proof.** For positive $r$, the constant $c=\sqrt r\,(2\pi)^{(1-r)/2}$ is positive and hence nonzero. For every $k\ge1$, the exact factorization identifies the matching Stirling core with $c$ times the matching core growth. Multiplication by a fixed nonzero constant preserves asymptotic growth order, so the two functions have the same order.

**Key facts.** `FABL.matchingStirlingCore_eq_constant_mul_growth`.
