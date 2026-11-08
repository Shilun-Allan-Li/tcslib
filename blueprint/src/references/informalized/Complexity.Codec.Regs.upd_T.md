<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the T register

**Claim.** Replacing coordinate $13$ of the register-value vector by $v$ gives the vector of values for the record with its $T$ register set to $v$.

**Proof.** It is enough to compare the vectors at every coordinate in the 21-element index set. At coordinate $13$, the updated vector has value $v$, exactly the $T$ value in the modified record. At all other coordinates, both vectors have the corresponding original register value. Thus the vectors agree at every coordinate.
