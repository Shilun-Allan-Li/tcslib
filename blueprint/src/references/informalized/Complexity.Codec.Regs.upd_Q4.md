<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_Q4 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the fourth query register

**Claim.** Replacing coordinate $18$ of the register-value vector by $v$ gives the vector of values for the record with its fourth query register set to $v$.

**Proof.** To prove equality of the two vectors, compare their values at an arbitrary coordinate. The index set has 21 elements, so checking its coordinates one by one suffices. At coordinate $18$, the update supplies $v$, matching the fourth query register in the modified record. At every other coordinate, both sides retain the original register value. Hence the vectors agree everywhere.
