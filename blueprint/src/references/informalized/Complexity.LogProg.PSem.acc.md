<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.acc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance at a True Return

**Claim.** If the instruction at $l$ deterministically returns true and the guard holds at the live configuration with valuation $v$ and no result, then that configuration has guarded terminating semantics with acceptance probability $1$.

**Proof.** The deterministic-return result (`PSem.ret`) gives semantics with probability $1$ for a true return, under the stated guard. The conclusion is that same probability, so the probability-congruence result (`PSem.congr`) transfers it directly.

**Key facts.** `Complexity.LogProg.PSem.ret`, `Complexity.LogProg.PSem.congr`.
