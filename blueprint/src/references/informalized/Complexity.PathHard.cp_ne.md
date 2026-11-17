<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.cp_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Copy Registers

**Claim.** For each of the twelve copy operations, its destination register differs from its source register.

**Proof.** The copy operation has twelve possible cases. In each case, the definitions of the destination and source select two different registers. Checking these finitely many pairs establishes the claim.
