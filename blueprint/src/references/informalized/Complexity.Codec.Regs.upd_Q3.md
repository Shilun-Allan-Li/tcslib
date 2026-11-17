<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_Q3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the third query register

**Claim.** Replacing coordinate $17$ of the register-value vector by $v$ gives the vector of values for the record with its third query register set to $v$.

**Proof.** To prove equality of the two vectors, compare their values at an arbitrary coordinate. Since the coordinates are the 21 elements of the finite index set, it suffices to check each one. At coordinate $17$, the update supplies $v$, which is also the third query register value in the modified record. At every other coordinate, the update leaves the original value unchanged, and modifying the third query register leaves that register value unchanged. Thus the vectors agree at every coordinate.
