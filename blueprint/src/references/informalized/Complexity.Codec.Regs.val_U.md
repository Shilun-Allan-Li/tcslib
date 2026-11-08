<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.val_U -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the U register

**Claim.** For every register record $R$, the value of its coordinate at index $14$ is the value stored in its $U$ register.

**Proof.** The index $r_U$ is $14$, and the coordinate function assigns the $U$ register to index $14$. Evaluating the definition at this index gives the claimed equality.
