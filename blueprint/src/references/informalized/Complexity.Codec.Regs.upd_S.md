<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_S -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the S register

**Claim.** Replacing coordinate $4$ of the register-value vector by $v$ gives the vector of values for the record with its $S$ register set to $v$.

**Proof.** Compare the two vectors at an arbitrary coordinate; equality of functions follows once their values agree at each of the 21 coordinates. At coordinate $4$, the update gives $v$, which is the $S$ register value in the modified record. At every other coordinate, the update preserves the original value, and changing $S$ does not affect those entries. Therefore the vectors are equal.
