<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.inc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of an Increment Step

**Claim.** If the instruction at $l$ increments register $r$ and moves to $l'$, the current configuration satisfies the guard, and the resulting configuration has probabilistic semantics with probability $p$, then the current configuration also has probabilistic semantics with probability $p$.

**Proof.** Apply the deterministic-step principle (Complexity.LogProg.PSem.det) to the increment instruction. Its one-step transition replaces $v(r)$ by $v(r)+1$, leaves the other registers unchanged, and moves to $l'$, so the successor is exactly the configuration in the hypothesis. The guard at the current configuration supplies the other required hypothesis, giving the conclusion.

**Key facts.** `Complexity.LogProg.PSem.det`.
