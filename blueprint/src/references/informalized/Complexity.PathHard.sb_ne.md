<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.sb_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subtraction Registers Avoid the Index Register

**Claim.** At each of the three subtraction sites, the associated register is distinct from the index register.

**Proof.** There are three cases for the subtraction site. Their associated registers are respectively the registers for $n$, $m$, and $t$, with indices $7$, $8$, and $3$; the index register has index $11$. Each pair is distinct, proving the claim.
