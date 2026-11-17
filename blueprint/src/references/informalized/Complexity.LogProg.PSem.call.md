<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of a Deterministic Oracle Call

**Claim.** When the instruction at $l$ is the specified deterministic oracle call, semantics of probability $p$ at the successor selected by the oracle implies semantics of probability $p$ at $l$.

**Proof.** A deterministic instruction preserves probabilistic semantics when its one-step successor has that semantics and the guard holds at the current configuration (`PSem.det`). For this call, the one-step transition keeps the register valuation and no-result field unchanged and moves to $l_1$ or $l_0$ according to the oracle's answer on the virtual input. This is precisely the successor configuration in the hypothesis, so applying the deterministic-step result proves the claim.

**Key facts.** `Complexity.LogProg.PSem.det`.
