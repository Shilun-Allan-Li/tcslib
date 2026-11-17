<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.jeq_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of the Unequal-Register Branch

**Claim.** If the instruction at $l$ branches to $l_1$ when registers $r,s$ are equal and to $l_0$ otherwise, the current configuration satisfies the guard, $v(r)\ne v(s)$, and the $l_0$ successor has probabilistic semantics with probability $p$, then the current configuration has probabilistic semantics with probability $p$.

**Proof.** Because the register values are unequal, the equality test selects the $l_0$ branch. The deterministic one-step transition therefore leaves the register assignment unchanged and moves to $l_0$. The assumed semantics is exactly that of this successor. Applying the deterministic-step principle (Complexity.LogProg.PSem.det), using the guard at the current configuration, proves the result.

**Key facts.** `Complexity.LogProg.PSem.det`.
