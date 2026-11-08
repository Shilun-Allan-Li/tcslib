<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_Wp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Wp register

**Claim.** For every register record $R$, the value of its coordinate at index $6$ is the value stored in its $Wp$ register.

**Proof.** The index $r_{Wp}$ is $6$, and the coordinate function assigns the $Wp$ register to index $6$. Evaluating the definition at this index gives the claimed equality.
