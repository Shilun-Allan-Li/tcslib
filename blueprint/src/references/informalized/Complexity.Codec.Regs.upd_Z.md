<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_Z -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Z register

**Claim.** Replacing coordinate $20$ of the register-value vector by $v$ gives the vector of values for the record with its $Z$ register set to $v$.

**Proof.** Check the two vectors at each coordinate. At coordinate $20$, the update gives $v$, which is the $Z$ value of the modified record. At all other coordinates, the update preserves the original value, as does changing only $Z$. Thus the vectors have equal entries everywhere.
