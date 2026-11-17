<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.Em.nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emission for an Empty Segment

**Claim.** If the initial configuration $a$ satisfies $P$, then the empty segment starting at $k$ satisfies the emission property from $a$ with postcondition $P$.

**Proof.** The halting clause would require $k\le i<k+|[]|=k$, which is impossible, so that clause holds vacuously. For the reachability clause, the condition $k+|[]|\le i$ merely supplies a situation in which an endpoint is needed; choose $a$ itself. It satisfies $P$ by hypothesis, and the zero-step reach from $a$ to itself is given by reflexivity of bounded reachability (`Complexity.LogProg.AReach.refl`).

**Key facts.** `Complexity.LogProg.AReach.refl`.
