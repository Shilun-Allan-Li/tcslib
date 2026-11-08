<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_U -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the U register

**Claim.** Replacing coordinate $14$ of the register-value vector by $v$ gives the vector of values for the record with its $U$ register set to $v$.

**Proof.** Compare values at an arbitrary coordinate, checking the 21 possible coordinates. At coordinate $14$, the update replaces the old value by $v$, which is the $U$ value of the modified record. At every other coordinate, the update leaves the original value in place, just as changing $U$ leaves those register values unchanged. Hence the vectors are equal.
