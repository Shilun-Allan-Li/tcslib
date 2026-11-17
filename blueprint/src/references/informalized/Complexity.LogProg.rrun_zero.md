<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean :: Complexity.LogProg.rrun_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Step Run

**Claim.** For every register program $P$ with oracle and every configuration $c$, the run of length zero from $c$ is $c$ itself.

**Proof.** A run of length zero is the zeroth iterate of the step function. The zeroth iterate is the identity, so it sends $c$ to $c$.
