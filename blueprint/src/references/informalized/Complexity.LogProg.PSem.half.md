<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of a Halving Step

**Claim.** If the instruction at $l$ halves register $r$ and moves to $l'$, the current configuration satisfies the guard, and the resulting configuration has probabilistic semantics with probability $p$, then the current configuration also has probabilistic semantics with probability $p$.

**Proof.** Apply the deterministic-step principle (Complexity.LogProg.PSem.det) to the halving instruction. Its one-step transition replaces $v(r)$ by $\lfloor v(r)/2\rfloor$, leaves the other registers unchanged, and moves to $l'$. Thus its successor is exactly the configuration in the hypothesis. Together with the guard at the current configuration, the deterministic-step principle gives probabilistic semantics there with the same probability.

**Key facts.** `Complexity.LogProg.PSem.det`.
