<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_Wp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Wp register

**Claim.** Replacing coordinate $6$ of the register-value vector by $v$ gives the vector of values for the record with its $Wp$ register set to $v$.

**Proof.** To establish vector equality, compare the entries at each of the 21 coordinates. At coordinate $6$, the update assigns $v$, matching the $Wp$ register in the modified record. Every other coordinate keeps its original value on both sides, since changing $Wp$ affects only that entry. The vectors therefore agree.
